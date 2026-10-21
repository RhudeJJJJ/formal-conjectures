/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2368 : Family 10 := level10.get ⟨1127,by decide⟩
def sourceMap2368 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2368 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2368_checked : acceptsGraphIso
    (source (graph core2368) (root 10) 0 0) DegreeOneSmallSpectrum1778.graph sourceMap2368=true := by decide +kernel
theorem fusedMap2368_checked : acceptsGraphIso
    (fused (graph core2368) (root 10) 0 0) DegreeOneSmallSpectrum1783.graph fusedMap2368=true := by decide +kernel
theorem certified2368 : Certified (graph core2368) (root 10) 0 0 :=
  of_native_maps core2368 DegreeOneSmallSpectrum1778.graph DegreeOneSmallSpectrum1783.graph
    sourceMap2368 fusedMap2368 sourceMap2368_checked fusedMap2368_checked
    DegreeOneSmallComparisons.comparison2368
#print axioms sourceMap2368_checked
#print axioms fusedMap2368_checked
#print axioms certified2368
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
