/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2191 : Family 10 := level10.get ⟨695,by decide⟩
def sourceMap2191 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2191 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2191_checked : acceptsGraphIso
    (source (graph core2191) (root 10) 0 0) DegreeOneSmallSpectrum1763.graph sourceMap2191=true := by decide +kernel
theorem fusedMap2191_checked : acceptsGraphIso
    (fused (graph core2191) (root 10) 0 0) DegreeOneSmallSpectrum1310.graph fusedMap2191=true := by decide +kernel
theorem certified2191 : Certified (graph core2191) (root 10) 0 0 :=
  of_native_maps core2191 DegreeOneSmallSpectrum1763.graph DegreeOneSmallSpectrum1310.graph
    sourceMap2191 fusedMap2191 sourceMap2191_checked fusedMap2191_checked
    DegreeOneSmallComparisons.comparison2191
#print axioms sourceMap2191_checked
#print axioms fusedMap2191_checked
#print axioms certified2191
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
