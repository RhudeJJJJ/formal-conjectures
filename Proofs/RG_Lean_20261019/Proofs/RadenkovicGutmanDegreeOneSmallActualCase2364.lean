/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2364 : Family 10 := level10.get ⟨1115,by decide⟩
def sourceMap2364 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,4,5,6,2,3] (sourceLabel 10 0 0 v)
def fusedMap2364 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2364_checked : acceptsGraphIso
    (source (graph core2364) (root 10) 0 0) DegreeOneSmallSpectrum1712.graph sourceMap2364=true := by decide +kernel
theorem fusedMap2364_checked : acceptsGraphIso
    (fused (graph core2364) (root 10) 0 0) DegreeOneSmallSpectrum1771.graph fusedMap2364=true := by decide +kernel
theorem certified2364 : Certified (graph core2364) (root 10) 0 0 :=
  of_native_maps core2364 DegreeOneSmallSpectrum1712.graph DegreeOneSmallSpectrum1771.graph
    sourceMap2364 fusedMap2364 sourceMap2364_checked fusedMap2364_checked
    DegreeOneSmallComparisons.comparison2364
#print axioms sourceMap2364_checked
#print axioms fusedMap2364_checked
#print axioms certified2364
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
