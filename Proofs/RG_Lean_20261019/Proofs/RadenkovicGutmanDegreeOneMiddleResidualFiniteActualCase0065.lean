/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0065 : Family 8 := level8.get ⟨6,by decide⟩
def sourceMap0065 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,1,0,10,11,12,13,14,9,3,4,5,6,7,8] (sourceLabel 8 2 2 v)
def fusedMap0065 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0065_checked : acceptsGraphIso
    (source (graph core0065) (root 8) 2 2) DegreeTwoThreeSpectrum2822.graph sourceMap0065=true := by decide +kernel
theorem fusedMap0065_checked : acceptsGraphIso
    (fused (graph core0065) (root 8) 2 2) DegreeTwoThreeSpectrum2314.graph fusedMap0065=true := by decide +kernel
theorem certified0065 : Certified (graph core0065) (root 8) 2 2 :=
  of_native_maps core0065 DegreeTwoThreeSpectrum2822.graph DegreeTwoThreeSpectrum2314.graph
    sourceMap0065 fusedMap0065 sourceMap0065_checked fusedMap0065_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0065
#print axioms sourceMap0065_checked
#print axioms fusedMap0065_checked
#print axioms certified0065
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
