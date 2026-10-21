/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2325 : Family 10 := level10.get ⟨1021,by decide⟩
def sourceMap2325 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (sourceLabel 10 0 0 v)
def fusedMap2325 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2325_checked : acceptsGraphIso
    (source (graph core2325) (root 10) 0 0) DegreeOneSmallSpectrum1586.graph sourceMap2325=true := by decide +kernel
theorem fusedMap2325_checked : acceptsGraphIso
    (fused (graph core2325) (root 10) 0 0) DegreeOneSmallSpectrum1598.graph fusedMap2325=true := by decide +kernel
theorem certified2325 : Certified (graph core2325) (root 10) 0 0 :=
  of_native_maps core2325 DegreeOneSmallSpectrum1586.graph DegreeOneSmallSpectrum1598.graph
    sourceMap2325 fusedMap2325 sourceMap2325_checked fusedMap2325_checked
    DegreeOneSmallComparisons.comparison2325
#print axioms sourceMap2325_checked
#print axioms fusedMap2325_checked
#print axioms certified2325
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
