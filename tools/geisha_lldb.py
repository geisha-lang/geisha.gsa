"""
LLDB Data Formatters for Geisha (.gsa) binaries compiled with `-g` / `--debug`.

Load in LLDB:
    command script import ~/.geisha/lib/geisha_lldb.py

Or add to ~/.lldbinit or VS Code CodeLLDB `initCommands`:
    command script import ~/.geisha/lib/geisha_lldb.py
"""

import struct
import lldb


def _read_c_string(process, addr, max_len=256):
    if addr == 0:
        return "null"
    err = lldb.SBError()
    raw = process.ReadCStringFromMemory(addr, max_len, err)
    if err.Fail():
        return f"<unreadable String @ 0x{addr:x}>"
    escaped = raw.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n").replace("\r", "\\r").replace("\t", "\\t")
    if len(raw) >= max_len - 1:
        return f'"{escaped}..."'
    return f'"{escaped}"'


def _format_elem(process, elem_type, addr, ptr_size):
    err = lldb.SBError()
    t = elem_type.strip()
    if t == "Int":
        data = process.ReadMemory(addr, 4, err)
        return str(struct.unpack("<i", data)[0]) if err.Success() else "?"
    if t == "Int64":
        data = process.ReadMemory(addr, 8, err)
        return str(struct.unpack("<q", data)[0]) if err.Success() else "?"
    if t == "Float":
        data = process.ReadMemory(addr, 8, err)
        return f"{struct.unpack('<d', data)[0]:g}" if err.Success() else "?"
    if t == "Float32":
        data = process.ReadMemory(addr, 4, err)
        return f"{struct.unpack('<f', data)[0]:g}" if err.Success() else "?"
    if t == "Bool":
        data = process.ReadMemory(addr, 1, err)
        return ("true" if data[0] != 0 else "false") if err.Success() else "?"
    if t == "Char":
        data = process.ReadMemory(addr, 1, err)
        return repr(chr(data[0])) if err.Success() else "?"
    if t == "String":
        p = process.ReadPointerFromMemory(addr, err)
        return _read_c_string(process, p) if err.Success() else "?"
    p = process.ReadPointerFromMemory(addr, err)
    return f"0x{p:x}" if err.Success() else "?"


def _elem_stride(elem_type, ptr_size):
    t = elem_type.strip()
    if t in ("Int", "Float32"):
        return 4
    if t in ("Int64", "Float"):
        return 8
    if t in ("Bool", "Char", "Void"):
        return 1
    return ptr_size


def geisha_string_summary(valobj, internal_dict):
    process = valobj.GetProcess()
    addr = valobj.GetValueAsUnsigned(0)
    return _read_c_string(process, addr)


def _extract_vec_elem_type(type_name):
    # Matches "std.vec.Vec (Int)" or "Vec (String)"
    lp = type_name.find("(")
    rp = type_name.rfind(")")
    if lp != -1 and rp > lp:
        return type_name[lp + 1 : rp].strip()
    return "ptr"


def geisha_vec_summary(valobj, internal_dict):
    process = valobj.GetProcess()
    ptr_size = process.GetAddressByteSize()
    err = lldb.SBError()

    arr_cell_child = valobj.GetChildMemberWithName("_0")
    len_cell_child = valobj.GetChildMemberWithName("_1")
    if not arr_cell_child.IsValid() or not len_cell_child.IsValid():
        return "<invalid Vec>"

    arr_cell_ptr = arr_cell_child.GetValueAsUnsigned(0)
    len_cell_ptr = len_cell_child.GetValueAsUnsigned(0)
    if arr_cell_ptr == 0 or len_cell_ptr == 0:
        return "Vec(null)"

    len_bytes = process.ReadMemory(len_cell_ptr, 4, err)
    if err.Fail():
        return "<unreadable Vec len>"
    vlen = struct.unpack("<i", len_bytes)[0]

    arr_ptr = process.ReadPointerFromMemory(arr_cell_ptr, err)
    if err.Fail() or arr_ptr == 0:
        return f"Vec(len={vlen})"

    elem_ty = _extract_vec_elem_type(valobj.GetTypeName())
    stride = _elem_stride(elem_ty, ptr_size)
    max_show = min(vlen, 8)
    elems = []
    for i in range(max_show):
        elems.append(_format_elem(process, elem_ty, arr_ptr + 8 + i * stride, ptr_size))
    suffix = ", ..." if vlen > max_show else ""
    return f"Vec(len={vlen}) [{', '.join(elems)}{suffix}]"


def geisha_array_summary(valobj, internal_dict):
    process = valobj.GetProcess()
    ptr_size = process.GetAddressByteSize()
    err = lldb.SBError()

    arr_ptr = valobj.GetValueAsUnsigned(0)
    if arr_ptr == 0:
        return "Array(null)"

    len_bytes = process.ReadMemory(arr_ptr, 8, err)
    if err.Fail():
        return "<unreadable Array>"
    alen = struct.unpack("<q", len_bytes)[0]

    tname = valobj.GetTypeName()
    lt = tname.find("<")
    gt = tname.rfind(">")
    elem_ty = tname[lt + 1 : gt].strip() if lt != -1 and gt > lt else "ptr"
    stride = _elem_stride(elem_ty, ptr_size)
    max_show = min(max(alen, 0), 8)
    elems = []
    for i in range(max_show):
        elems.append(_format_elem(process, elem_ty, arr_ptr + 8 + i * stride, ptr_size))
    suffix = ", ..." if alen > max_show else ""
    return f"Array(len={alen}) [{', '.join(elems)}{suffix}]"


def geisha_adt_summary(valobj, internal_dict):
    process = valobj.GetProcess()
    ptr_size = process.GetAddressByteSize()
    err = lldb.SBError()

    adt_ptr = valobj.GetValueAsUnsigned(0)
    if adt_ptr == 0:
        return "null"

    tname = valobj.GetTypeName()
    lt = tname.find("<")
    gt = tname.rfind(">")
    inner = tname[lt + 1 : gt].strip() if lt != -1 and gt > lt else tname

    tag_bytes = process.ReadMemory(adt_ptr, 4, err)
    if err.Fail():
        return f"{inner} @ 0x{adt_ptr:x}"
    tag = struct.unpack("<i", tag_bytes)[0]

    # Special pretty-printing for `List (T)`: tag 0 = Nil, tag 1 = Cons(head, tail)
    if inner.startswith("List (") and inner.endswith(")"):
        elem_ty = inner[6:-1].strip()
        items = []
        cur = adt_ptr
        steps = 0
        while cur != 0 and steps < 16:
            tb = process.ReadMemory(cur, 4, err)
            if err.Fail():
                break
            t = struct.unpack("<i", tb)[0]
            if t == 0:
                break
            head_str = _format_elem(process, elem_ty, cur + 8, ptr_size)
            items.append(head_str)
            tail_off = 16 if _elem_stride(elem_ty, ptr_size) <= 8 else 8 + _elem_stride(elem_ty, ptr_size)
            cur = process.ReadPointerFromMemory(cur + tail_off, err)
            if err.Fail():
                break
            steps += 1
        suffix = ", ..." if steps == 16 and cur != 0 else ""
        return f"[{', '.join(items)}{suffix}]"

    # Special pretty-printing for `std.option.Option (T)` / `Option (T)`: tag 0 = None, tag 1 = Some(x)
    if "Option (" in inner and inner.endswith(")"):
        if tag == 0:
            return "None"
        lp = inner.find("(")
        elem_ty = inner[lp + 1 : -1].strip()
        pay_off = 8 if _elem_stride(elem_ty, ptr_size) >= 8 else 4
        val_str = _format_elem(process, elem_ty, adt_ptr + pay_off, ptr_size)
        return f"Some({val_str})"

    # Generic boxed ADT: use DWARF `payload` member (exact 4-byte or 8-byte offset)
    deref = valobj.Dereference()
    pay_child = deref.GetChildMemberWithName("payload") if deref.IsValid() else None
    if pay_child and pay_child.IsValid():
        psize = pay_child.GetByteSize()
        pval = pay_child.GetValueAsSigned(0)
        if psize == 4:
            return f"{inner}(tag={tag}, payload={pval})"
        if -2147483648 <= pval <= 2147483647:
            return f"{inner}(tag={tag}, payload={pval})"
        return f"{inner}(tag={tag}, payload=0x{pval & 0xFFFFFFFFFFFFFFFF:x})"
    return f"{inner}(tag={tag})"


def __lldb_init_module(debugger, internal_dict):
    debugger.HandleCommand(
        'type summary add -F geisha_lldb.geisha_string_summary -w geisha "String"'
    )
    debugger.HandleCommand(
        'type summary add -F geisha_lldb.geisha_vec_summary -w geisha -x "^(std\\.vec\\.)?Vec \\(.*\\)$"'
    )
    debugger.HandleCommand(
        'type summary add -F geisha_lldb.geisha_array_summary -w geisha -x "^gs_array<.*> \\*$"'
    )
    debugger.HandleCommand(
        'type summary add -F geisha_lldb.geisha_adt_summary -w geisha -x "^gs_adt<.*> \\*$"'
    )
    debugger.HandleCommand("type category enable geisha")
    print("Geisha LLDB formatters loaded (String, Vec, MutArray/ImmArray, List/Option/ADT).")
