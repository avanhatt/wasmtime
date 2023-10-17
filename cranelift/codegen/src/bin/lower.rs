use cranelift_codegen::{
    dominator_tree::DominatorTree,
    flowgraph::ControlFlowGraph,
    ir::{types::I64, Function},
    isa::aarch64::{
        abi,
        inst::emit::EmitInfo,
        lower::isle::generated_code::{constructor_a64_udiv, MInst},
        settings as aarch64_settings, AArch64Backend,
    },
    machinst::{isle::IsleContext, BlockLoweringOrder, Lower, SigSet, VRegAllocator},
    settings as shared_settings,
};
use cranelift_control::ControlPlane;
use target_lexicon::triple;

fn main() {
    // Construct a lowering context for AArch64.
    let shared_flags_builder = shared_settings::builder();
    let shared_flags = shared_settings::Flags::new(shared_flags_builder);

    let isa_flags_builder = aarch64_settings::builder();
    let isa_flags = aarch64_settings::Flags::new(&shared_flags, &isa_flags_builder);

    let backend =
        AArch64Backend::new_with_flags(triple!("aarch64"), shared_flags.clone(), isa_flags.clone());

    let f = Function::new();
    let emit_info = EmitInfo::new(shared_flags.clone());
    let sigs = SigSet::new::<abi::AArch64MachineDeps>(&f, &shared_flags).unwrap();
    let abi = abi::AArch64Callee::new(&f, &backend, &isa_flags, &sigs).unwrap();

    let cfg = ControlFlowGraph::with_function(&f);
    let domtree = DominatorTree::with_function(&f, &cfg);
    let mut ctrl_plane = ControlPlane::default();
    let block_order = BlockLoweringOrder::new(&f, &domtree, &mut ctrl_plane);

    let mut lower = Lower::<MInst>::new(&f, abi, emit_info, block_order, sigs).unwrap();

    // Construct an ISLE Context.
    let mut ctx = IsleContext {
        lower_ctx: &mut lower,
        backend: &backend,
    };

    // Lower an instruction.
    let mut vreg_alloc = VRegAllocator::<MInst>::new();
    let v1 = vreg_alloc.alloc(I64).unwrap().only_reg().unwrap();
    let v2 = vreg_alloc.alloc(I64).unwrap().only_reg().unwrap();
    constructor_a64_udiv(&mut ctx, I64, v1, v2);
}
