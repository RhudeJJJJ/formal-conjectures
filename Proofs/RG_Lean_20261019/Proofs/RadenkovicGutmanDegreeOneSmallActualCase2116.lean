/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2116 : Family 10 := level10.get ⟨543,by decide⟩
def sourceMap2116 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,10,11,8,9] (sourceLabel 10 0 0 v)
def fusedMap2116 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2116_checked : acceptsGraphIso
    (source (graph core2116) (root 10) 0 0) DegreeOneSmallSpectrum1678.graph sourceMap2116=true := by decide +kernel
theorem fusedMap2116_checked : acceptsGraphIso
    (fused (graph core2116) (root 10) 0 0) DegreeOneSmallSpectrum1057.graph fusedMap2116=true := by decide +kernel
theorem certified2116 : Certified (graph core2116) (root 10) 0 0 :=
  of_native_maps core2116 DegreeOneSmallSpectrum1678.graph DegreeOneSmallSpectrum1057.graph
    sourceMap2116 fusedMap2116 sourceMap2116_checked fusedMap2116_checked
    DegreeOneSmallComparisons.comparison2116
#print axioms sourceMap2116_checked
#print axioms fusedMap2116_checked
#print axioms certified2116
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
