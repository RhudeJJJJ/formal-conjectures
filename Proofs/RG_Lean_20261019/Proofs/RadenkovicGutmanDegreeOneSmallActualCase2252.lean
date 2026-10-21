/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2252 : Family 10 := level10.get ⟨813,by decide⟩
def sourceMap2252 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,5,6,7,8,3,4] (sourceLabel 10 0 0 v)
def fusedMap2252 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2252_checked : acceptsGraphIso
    (source (graph core2252) (root 10) 0 0) DegreeOneSmallSpectrum1782.graph sourceMap2252=true := by decide +kernel
theorem fusedMap2252_checked : acceptsGraphIso
    (fused (graph core2252) (root 10) 0 0) DegreeOneSmallSpectrum1447.graph fusedMap2252=true := by decide +kernel
theorem certified2252 : Certified (graph core2252) (root 10) 0 0 :=
  of_native_maps core2252 DegreeOneSmallSpectrum1782.graph DegreeOneSmallSpectrum1447.graph
    sourceMap2252 fusedMap2252 sourceMap2252_checked fusedMap2252_checked
    DegreeOneSmallComparisons.comparison2252
#print axioms sourceMap2252_checked
#print axioms fusedMap2252_checked
#print axioms certified2252
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
