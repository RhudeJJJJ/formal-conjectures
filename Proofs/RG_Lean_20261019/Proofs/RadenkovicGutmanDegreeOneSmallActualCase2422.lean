/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2422 : Family 10 := level10.get ⟨1307,by decide⟩
def sourceMap2422 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,4,5,6,2,3] (sourceLabel 10 0 0 v)
def fusedMap2422 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2422_checked : acceptsGraphIso
    (source (graph core2422) (root 10) 0 0) DegreeOneSmallSpectrum1750.graph sourceMap2422=true := by decide +kernel
theorem fusedMap2422_checked : acceptsGraphIso
    (fused (graph core2422) (root 10) 0 0) DegreeOneSmallSpectrum1944.graph fusedMap2422=true := by decide +kernel
theorem certified2422 : Certified (graph core2422) (root 10) 0 0 :=
  of_native_maps core2422 DegreeOneSmallSpectrum1750.graph DegreeOneSmallSpectrum1944.graph
    sourceMap2422 fusedMap2422 sourceMap2422_checked fusedMap2422_checked
    DegreeOneSmallComparisons.comparison2422
#print axioms sourceMap2422_checked
#print axioms fusedMap2422_checked
#print axioms certified2422
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
