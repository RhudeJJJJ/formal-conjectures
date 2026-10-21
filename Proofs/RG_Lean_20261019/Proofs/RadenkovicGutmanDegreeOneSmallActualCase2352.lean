/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2352 : Family 10 := level10.get ⟨1094,by decide⟩
def sourceMap2352 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (sourceLabel 10 0 0 v)
def fusedMap2352 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2352_checked : acceptsGraphIso
    (source (graph core2352) (root 10) 0 0) DegreeOneSmallSpectrum1699.graph sourceMap2352=true := by decide +kernel
theorem fusedMap2352_checked : acceptsGraphIso
    (fused (graph core2352) (root 10) 0 0) DegreeOneSmallSpectrum1701.graph fusedMap2352=true := by decide +kernel
theorem certified2352 : Certified (graph core2352) (root 10) 0 0 :=
  of_native_maps core2352 DegreeOneSmallSpectrum1699.graph DegreeOneSmallSpectrum1701.graph
    sourceMap2352 fusedMap2352 sourceMap2352_checked fusedMap2352_checked
    DegreeOneSmallComparisons.comparison2352
#print axioms sourceMap2352_checked
#print axioms fusedMap2352_checked
#print axioms certified2352
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
