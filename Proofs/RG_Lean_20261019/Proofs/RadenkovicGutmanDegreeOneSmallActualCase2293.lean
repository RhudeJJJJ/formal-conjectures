/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2293 : Family 10 := level10.get ⟨925,by decide⟩
def sourceMap2293 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2293 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2293_checked : acceptsGraphIso
    (source (graph core2293) (root 10) 0 0) DegreeOneSmallSpectrum1513.graph sourceMap2293=true := by decide +kernel
theorem fusedMap2293_checked : acceptsGraphIso
    (fused (graph core2293) (root 10) 0 0) DegreeOneSmallSpectrum1511.graph fusedMap2293=true := by decide +kernel
theorem certified2293 : Certified (graph core2293) (root 10) 0 0 :=
  of_native_maps core2293 DegreeOneSmallSpectrum1513.graph DegreeOneSmallSpectrum1511.graph
    sourceMap2293 fusedMap2293 sourceMap2293_checked fusedMap2293_checked
    DegreeOneSmallComparisons.comparison2293
#print axioms sourceMap2293_checked
#print axioms fusedMap2293_checked
#print axioms certified2293
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
