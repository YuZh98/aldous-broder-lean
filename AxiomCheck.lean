-- Axiom audit: run `lake env lean AxiomCheck.lean`. Each theorem must
-- depend only on [propext, Classical.choice, Quot.sound];
-- `scripts/check_axioms.py` enforces this.
import EAB

-- The endpoints.
#print axioms EAB.Paper.order_mass_identity
#print axioms EAB.Paper.Chain.aldous_broder
#print axioms EAB.Paper.Chain.aldous_broder_normalized
#print axioms EAB.Paper.Chain.stopped_forest_law

-- Their principal proof obligations.
#print axioms EAB.Paper.Foundation.one_vertex_transfer
#print axioms EAB.Paper.Foundation.one_vertex_transfer_singleton
#print axioms EAB.Paper.single_root_normalization
#print axioms EAB.Paper.Chain.confined_det_pos
#print axioms EAB.Paper.Chain.IsStationary.cofactorVec_eq
#print axioms EAB.Paper.Chain.green_reversal
#print axioms EAB.Paper.Chain.chainLaw_cylinder
#print axioms EAB.Paper.Chain.chainLaw_prefix_inter_shift
#print axioms EAB.Paper.Chain.ae_hits_all
#print axioms EAB.Paper.Chain.chainLaw_orderEvent
#print axioms EAB.Paper.Chain.chainLaw_orderEvent_eq
#print axioms EAB.Paper.Chain.chainLaw_forestEvent_marginal
