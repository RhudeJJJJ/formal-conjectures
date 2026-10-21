/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2224 : Family 10 := level10.get ⟨755,by decide⟩
def sourceMap2224 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2224 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2224_checked : acceptsGraphIso
    (source (graph core2224) (root 10) 0 0) DegreeOneSmallSpectrum1790.graph sourceMap2224=true := by decide +kernel
theorem fusedMap2224_checked : acceptsGraphIso
    (fused (graph core2224) (root 10) 0 0) DegreeOneSmallSpectrum1389.graph fusedMap2224=true := by decide +kernel
theorem certified2224 : Certified (graph core2224) (root 10) 0 0 :=
  of_native_maps core2224 DegreeOneSmallSpectrum1790.graph DegreeOneSmallSpectrum1389.graph
    sourceMap2224 fusedMap2224 sourceMap2224_checked fusedMap2224_checked
    DegreeOneSmallComparisons.comparison2224
#print axioms sourceMap2224_checked
#print axioms fusedMap2224_checked
#print axioms certified2224
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
