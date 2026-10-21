/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2349 : Family 10 := level10.get ⟨1072,by decide⟩
def sourceMap2349 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,9,10,11,12,7,8] (sourceLabel 10 0 0 v)
def fusedMap2349 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2349_checked : acceptsGraphIso
    (source (graph core2349) (root 10) 0 0) DegreeOneSmallSpectrum1672.graph sourceMap2349=true := by decide +kernel
theorem fusedMap2349_checked : acceptsGraphIso
    (fused (graph core2349) (root 10) 0 0) DegreeOneSmallSpectrum1694.graph fusedMap2349=true := by decide +kernel
theorem certified2349 : Certified (graph core2349) (root 10) 0 0 :=
  of_native_maps core2349 DegreeOneSmallSpectrum1672.graph DegreeOneSmallSpectrum1694.graph
    sourceMap2349 fusedMap2349 sourceMap2349_checked fusedMap2349_checked
    DegreeOneSmallComparisons.comparison2349
#print axioms sourceMap2349_checked
#print axioms fusedMap2349_checked
#print axioms certified2349
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
