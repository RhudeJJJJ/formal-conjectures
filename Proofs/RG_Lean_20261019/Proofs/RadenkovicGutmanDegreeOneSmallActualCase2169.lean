/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2169 : Family 10 := level10.get ⟨641,by decide⟩
def sourceMap2169 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,6,0,1,2,3,4,5,7,8,9,11,12] (sourceLabel 10 0 0 v)
def fusedMap2169 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2169_checked : acceptsGraphIso
    (source (graph core2169) (root 10) 0 0) DegreeOneSmallSpectrum1240.graph sourceMap2169=true := by decide +kernel
theorem fusedMap2169_checked : acceptsGraphIso
    (fused (graph core2169) (root 10) 0 0) DegreeOneSmallSpectrum1239.graph fusedMap2169=true := by decide +kernel
theorem certified2169 : Certified (graph core2169) (root 10) 0 0 :=
  of_native_maps core2169 DegreeOneSmallSpectrum1240.graph DegreeOneSmallSpectrum1239.graph
    sourceMap2169 fusedMap2169 sourceMap2169_checked fusedMap2169_checked
    DegreeOneSmallComparisons.comparison2169
#print axioms sourceMap2169_checked
#print axioms fusedMap2169_checked
#print axioms certified2169
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
