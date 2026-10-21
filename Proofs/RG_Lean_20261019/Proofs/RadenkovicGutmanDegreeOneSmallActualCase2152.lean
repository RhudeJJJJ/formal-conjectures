/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2152 : Family 10 := level10.get ⟨607,by decide⟩
def sourceMap2152 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2152 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2152_checked : acceptsGraphIso
    (source (graph core2152) (root 10) 0 0) DegreeOneSmallSpectrum1785.graph sourceMap2152=true := by decide +kernel
theorem fusedMap2152_checked : acceptsGraphIso
    (fused (graph core2152) (root 10) 0 0) DegreeOneSmallSpectrum1178.graph fusedMap2152=true := by decide +kernel
theorem certified2152 : Certified (graph core2152) (root 10) 0 0 :=
  of_native_maps core2152 DegreeOneSmallSpectrum1785.graph DegreeOneSmallSpectrum1178.graph
    sourceMap2152 fusedMap2152 sourceMap2152_checked fusedMap2152_checked
    DegreeOneSmallComparisons.comparison2152
#print axioms sourceMap2152_checked
#print axioms fusedMap2152_checked
#print axioms certified2152
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
