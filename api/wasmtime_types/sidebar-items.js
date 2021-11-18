initSidebarItems({"enum":[["EntityIndex","An index of an entity."],["EntityType","A type of an item in a wasm module where an item is typically something that can be exported."],["GlobalInit","Globals are initialized via the `const` operators or by referring to another import."],["WasmError","A WebAssembly translation error."],["WasmType","WebAssembly value type – equivalent of `wasmparser`’s Type."]],"macro":[["wasm_unsupported","Return an `Err(WasmError::Unsupported(msg))` where `msg` the string built by calling `format!` on the arguments to this macro."]],"struct":[["DataIndex","Index type of a passive data segment inside the WebAssembly module."],["DefinedFuncIndex","Index type of a defined function inside the WebAssembly module."],["DefinedGlobalIndex","Index type of a defined global inside the WebAssembly module."],["DefinedMemoryIndex","Index type of a defined memory inside the WebAssembly module."],["DefinedTableIndex","Index type of a defined table inside the WebAssembly module."],["ElemIndex","Index type of a passive element segment inside the WebAssembly module."],["FuncIndex","Index type of a function (imported or defined) inside the WebAssembly module."],["Global","A WebAssembly global."],["GlobalIndex","Index type of a global variable (imported or defined) inside the WebAssembly module."],["InstanceIndex","Index type of an instance inside the WebAssembly module."],["InstanceTypeIndex","Specialized index for just instance types."],["Memory","WebAssembly linear memory."],["MemoryIndex","Index type of a linear memory (imported or defined) inside the WebAssembly module."],["ModuleIndex","Index type of a module inside the WebAssembly module."],["ModuleTypeIndex","Specialized index for just module types."],["SignatureIndex","Index type of a signature (imported or defined) inside the WebAssembly module."],["Table","WebAssembly table."],["TableIndex","Index type of a table (imported or defined) inside the WebAssembly module."],["Tag","WebAssembly event."],["TagIndex","Index type of an event inside the WebAssembly module."],["TypeIndex","Index type of a type inside the WebAssembly module."],["WasmFuncType","WebAssembly function type – equivalent of `wasmparser`’s FuncType."]],"type":[["WasmResult","A convenient alias for a `Result` that uses `WasmError` as the error type."]]});