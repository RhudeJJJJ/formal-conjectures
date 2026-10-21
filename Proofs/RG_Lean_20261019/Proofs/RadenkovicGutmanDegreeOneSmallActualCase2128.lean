/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2128 : Family 10 := level10.get ⟨568,by decide⟩
def sourceMap2128 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2128 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2128_checked : acceptsGraphIso
    (source (graph core2128) (root 10) 0 0) DegreeOneSmallSpectrum1759.graph sourceMap2128=true := by decide +kernel
theorem fusedMap2128_checked : acceptsGraphIso
    (fused (graph core2128) (root 10) 0 0) DegreeOneSmallSpectrum1096.graph fusedMap2128=true := by decide +kernel
theorem certified2128 : Certified (graph core2128) (root 10) 0 0 :=
  of_native_maps core2128 DegreeOneSmallSpectrum1759.graph DegreeOneSmallSpectrum1096.graph
    sourceMap2128 fusedMap2128 sourceMap2128_checked fusedMap2128_checked
    DegreeOneSmallComparisons.comparison2128
#print axioms sourceMap2128_checked
#print axioms fusedMap2128_checked
#print axioms certified2128
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
