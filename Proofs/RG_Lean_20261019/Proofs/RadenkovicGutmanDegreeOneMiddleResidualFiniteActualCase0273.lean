/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0273 : Family 9 := level9.get ⟨99,by decide⟩
def sourceMap0273 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0273 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0273_checked : acceptsGraphIso
    (source (graph core0273) (root 9) 2 2) DegreeOneMiddleResidualSpectrum713.graph sourceMap0273=true := by decide +kernel
theorem fusedMap0273_checked : acceptsGraphIso
    (fused (graph core0273) (root 9) 2 2) DegreeOneMiddleResidualSpectrum517.graph fusedMap0273=true := by decide +kernel
theorem certified0273 : Certified (graph core0273) (root 9) 2 2 :=
  of_native_maps core0273 DegreeOneMiddleResidualSpectrum713.graph DegreeOneMiddleResidualSpectrum517.graph
    sourceMap0273 fusedMap0273 sourceMap0273_checked fusedMap0273_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0273
#print axioms sourceMap0273_checked
#print axioms fusedMap0273_checked
#print axioms certified0273
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
