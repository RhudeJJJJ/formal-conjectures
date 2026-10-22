/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0076 : Family 8 := level8.get ⟨20,by decide⟩
def sourceMap0076 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap0076 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0076_checked : acceptsGraphIso
    (source (graph core0076) (root 8) 2 2) DegreeOneMiddleResidualSpectrum240.graph sourceMap0076=true := by decide +kernel
theorem fusedMap0076_checked : acceptsGraphIso
    (fused (graph core0076) (root 8) 2 2) DegreeTwoThreeSpectrum2387.graph fusedMap0076=true := by decide +kernel
theorem certified0076 : Certified (graph core0076) (root 8) 2 2 :=
  of_native_maps core0076 DegreeOneMiddleResidualSpectrum240.graph DegreeTwoThreeSpectrum2387.graph
    sourceMap0076 fusedMap0076 sourceMap0076_checked fusedMap0076_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0076
#print axioms sourceMap0076_checked
#print axioms fusedMap0076_checked
#print axioms certified0076
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
