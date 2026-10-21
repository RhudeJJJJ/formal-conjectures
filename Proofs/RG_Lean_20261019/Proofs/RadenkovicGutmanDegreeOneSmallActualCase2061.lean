/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2061 : Family 10 := level10.get ⟨436,by decide⟩
def sourceMap2061 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2061 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2061_checked : acceptsGraphIso
    (source (graph core2061) (root 10) 0 0) DegreeOneSmallSpectrum1137.graph sourceMap2061=true := by decide +kernel
theorem fusedMap2061_checked : acceptsGraphIso
    (fused (graph core2061) (root 10) 0 0) DegreeOneSmallSpectrum1505.graph fusedMap2061=true := by decide +kernel
theorem certified2061 : Certified (graph core2061) (root 10) 0 0 :=
  of_native_maps core2061 DegreeOneSmallSpectrum1137.graph DegreeOneSmallSpectrum1505.graph
    sourceMap2061 fusedMap2061 sourceMap2061_checked fusedMap2061_checked
    DegreeOneSmallComparisons.comparison2061
#print axioms sourceMap2061_checked
#print axioms fusedMap2061_checked
#print axioms certified2061
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
