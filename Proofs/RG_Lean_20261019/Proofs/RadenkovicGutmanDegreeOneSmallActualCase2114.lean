/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2114 : Family 10 := level10.get ⟨540,by decide⟩
def sourceMap2114 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (sourceLabel 10 0 0 v)
def fusedMap2114 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2114_checked : acceptsGraphIso
    (source (graph core2114) (root 10) 0 0) DegreeOneSmallSpectrum1680.graph sourceMap2114=true := by decide +kernel
theorem fusedMap2114_checked : acceptsGraphIso
    (fused (graph core2114) (root 10) 0 0) DegreeOneSmallSpectrum1048.graph fusedMap2114=true := by decide +kernel
theorem certified2114 : Certified (graph core2114) (root 10) 0 0 :=
  of_native_maps core2114 DegreeOneSmallSpectrum1680.graph DegreeOneSmallSpectrum1048.graph
    sourceMap2114 fusedMap2114 sourceMap2114_checked fusedMap2114_checked
    DegreeOneSmallComparisons.comparison2114
#print axioms sourceMap2114_checked
#print axioms fusedMap2114_checked
#print axioms certified2114
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
