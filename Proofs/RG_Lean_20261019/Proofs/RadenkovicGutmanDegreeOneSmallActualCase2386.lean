/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2386 : Family 10 := level10.get ⟨1179,by decide⟩
def sourceMap2386 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2386 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2386_checked : acceptsGraphIso
    (source (graph core2386) (root 10) 0 0) DegreeOneSmallSpectrum1872.graph sourceMap2386=true := by decide +kernel
theorem fusedMap2386_checked : acceptsGraphIso
    (fused (graph core2386) (root 10) 0 0) DegreeOneSmallSpectrum1870.graph fusedMap2386=true := by decide +kernel
theorem certified2386 : Certified (graph core2386) (root 10) 0 0 :=
  of_native_maps core2386 DegreeOneSmallSpectrum1872.graph DegreeOneSmallSpectrum1870.graph
    sourceMap2386 fusedMap2386 sourceMap2386_checked fusedMap2386_checked
    DegreeOneSmallComparisons.comparison2386
#print axioms sourceMap2386_checked
#print axioms fusedMap2386_checked
#print axioms certified2386
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
