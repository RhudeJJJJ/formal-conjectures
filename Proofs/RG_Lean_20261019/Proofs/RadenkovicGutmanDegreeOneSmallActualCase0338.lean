/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0338 : Family 6 := level6.get ⟨8,by decide⟩
def sourceMap0338 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (sourceLabel 6 2 2 v)
def fusedMap0338 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap0338_checked : acceptsGraphIso
    (source (graph core0338) (root 6) 2 2) DegreeOneSmallSpectrum1239.graph sourceMap0338=true := by decide +kernel
theorem fusedMap0338_checked : acceptsGraphIso
    (fused (graph core0338) (root 6) 2 2) DegreeOneSmallSpectrum887.graph fusedMap0338=true := by decide +kernel
theorem certified0338 : Certified (graph core0338) (root 6) 2 2 :=
  of_native_maps core0338 DegreeOneSmallSpectrum1239.graph DegreeOneSmallSpectrum887.graph
    sourceMap0338 fusedMap0338 sourceMap0338_checked fusedMap0338_checked
    DegreeOneSmallComparisons.comparison0338
#print axioms sourceMap0338_checked
#print axioms fusedMap0338_checked
#print axioms certified0338
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
