/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2173 : Family 10 := level10.get ⟨653,by decide⟩
def sourceMap2173 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (sourceLabel 10 0 0 v)
def fusedMap2173 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2173_checked : acceptsGraphIso
    (source (graph core2173) (root 10) 0 0) DegreeOneSmallSpectrum1289.graph sourceMap2173=true := by decide +kernel
theorem fusedMap2173_checked : acceptsGraphIso
    (fused (graph core2173) (root 10) 0 0) DegreeOneSmallSpectrum1288.graph fusedMap2173=true := by decide +kernel
theorem certified2173 : Certified (graph core2173) (root 10) 0 0 :=
  of_native_maps core2173 DegreeOneSmallSpectrum1289.graph DegreeOneSmallSpectrum1288.graph
    sourceMap2173 fusedMap2173 sourceMap2173_checked fusedMap2173_checked
    DegreeOneSmallComparisons.comparison2173
#print axioms sourceMap2173_checked
#print axioms fusedMap2173_checked
#print axioms certified2173
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
