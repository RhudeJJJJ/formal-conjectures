/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0850 : Family 10 := level10.get ⟨577,by decide⟩
def sourceMap0850 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0850 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0850_checked : acceptsGraphIso
    (source (graph core0850) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2066.graph sourceMap0850=true := by decide +kernel
theorem fusedMap0850_checked : acceptsGraphIso
    (fused (graph core0850) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1138.graph fusedMap0850=true := by decide +kernel
theorem certified0850 : Certified (graph core0850) (root 10) 2 2 :=
  of_native_maps core0850 DegreeOneMiddleResidualSpectrum2066.graph DegreeOneMiddleResidualSpectrum1138.graph
    sourceMap0850 fusedMap0850 sourceMap0850_checked fusedMap0850_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0850
#print axioms sourceMap0850_checked
#print axioms fusedMap0850_checked
#print axioms certified0850
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
