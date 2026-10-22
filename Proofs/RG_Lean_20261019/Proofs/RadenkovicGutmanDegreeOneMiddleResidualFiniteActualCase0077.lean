/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0077 : Family 8 := level8.get ⟨21,by decide⟩
def sourceMap0077 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap0077 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0077_checked : acceptsGraphIso
    (source (graph core0077) (root 8) 2 2) DegreeTwoThreeSpectrum2823.graph sourceMap0077=true := by decide +kernel
theorem fusedMap0077_checked : acceptsGraphIso
    (fused (graph core0077) (root 8) 2 2) DegreeTwoThreeSpectrum2393.graph fusedMap0077=true := by decide +kernel
theorem certified0077 : Certified (graph core0077) (root 8) 2 2 :=
  of_native_maps core0077 DegreeTwoThreeSpectrum2823.graph DegreeTwoThreeSpectrum2393.graph
    sourceMap0077 fusedMap0077 sourceMap0077_checked fusedMap0077_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0077
#print axioms sourceMap0077_checked
#print axioms fusedMap0077_checked
#print axioms certified0077
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
