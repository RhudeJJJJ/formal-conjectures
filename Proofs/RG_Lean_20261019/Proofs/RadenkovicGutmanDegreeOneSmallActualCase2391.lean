/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2391 : Family 10 := level10.get ⟨1189,by decide⟩
def sourceMap2391 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,4,5,6,7,8,2,3] (sourceLabel 10 0 0 v)
def fusedMap2391 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,12,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap2391_checked : acceptsGraphIso
    (source (graph core2391) (root 10) 0 0) DegreeOneSmallSpectrum1699.graph sourceMap2391=true := by decide +kernel
theorem fusedMap2391_checked : acceptsGraphIso
    (fused (graph core2391) (root 10) 0 0) DegreeOneSmallSpectrum1880.graph fusedMap2391=true := by decide +kernel
theorem certified2391 : Certified (graph core2391) (root 10) 0 0 :=
  of_native_maps core2391 DegreeOneSmallSpectrum1699.graph DegreeOneSmallSpectrum1880.graph
    sourceMap2391 fusedMap2391 sourceMap2391_checked fusedMap2391_checked
    DegreeOneSmallComparisons.comparison2391
#print axioms sourceMap2391_checked
#print axioms fusedMap2391_checked
#print axioms certified2391
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
