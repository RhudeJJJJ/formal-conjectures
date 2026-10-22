/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0084 : Family 8 := level8.get ⟨30,by decide⟩
def sourceMap0084 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,8,9,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap0084 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0084_checked : acceptsGraphIso
    (source (graph core0084) (root 8) 2 2) DegreeTwoThreeSpectrum2820.graph sourceMap0084=true := by decide +kernel
theorem fusedMap0084_checked : acceptsGraphIso
    (fused (graph core0084) (root 8) 2 2) DegreeTwoThreeSpectrum2433.graph fusedMap0084=true := by decide +kernel
theorem certified0084 : Certified (graph core0084) (root 8) 2 2 :=
  of_native_maps core0084 DegreeTwoThreeSpectrum2820.graph DegreeTwoThreeSpectrum2433.graph
    sourceMap0084 fusedMap0084 sourceMap0084_checked fusedMap0084_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0084
#print axioms sourceMap0084_checked
#print axioms fusedMap0084_checked
#print axioms certified0084
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
