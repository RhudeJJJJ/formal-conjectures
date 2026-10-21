/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2153 : Family 10 := level10.get ⟨615,by decide⟩
def sourceMap2153 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2153 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2153_checked : acceptsGraphIso
    (source (graph core2153) (root 10) 0 0) DegreeOneSmallSpectrum1839.graph sourceMap2153=true := by decide +kernel
theorem fusedMap2153_checked : acceptsGraphIso
    (fused (graph core2153) (root 10) 0 0) DegreeOneSmallSpectrum1183.graph fusedMap2153=true := by decide +kernel
theorem certified2153 : Certified (graph core2153) (root 10) 0 0 :=
  of_native_maps core2153 DegreeOneSmallSpectrum1839.graph DegreeOneSmallSpectrum1183.graph
    sourceMap2153 fusedMap2153 sourceMap2153_checked fusedMap2153_checked
    DegreeOneSmallComparisons.comparison2153
#print axioms sourceMap2153_checked
#print axioms fusedMap2153_checked
#print axioms certified2153
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
