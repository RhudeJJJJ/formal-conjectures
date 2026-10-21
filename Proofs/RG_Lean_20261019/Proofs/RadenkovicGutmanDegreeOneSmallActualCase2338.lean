/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2338 : Family 10 := level10.get ⟨1048,by decide⟩
def sourceMap2338 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2338 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2338_checked : acceptsGraphIso
    (source (graph core2338) (root 10) 0 0) DegreeOneSmallSpectrum1647.graph sourceMap2338=true := by decide +kernel
theorem fusedMap2338_checked : acceptsGraphIso
    (fused (graph core2338) (root 10) 0 0) DegreeOneSmallSpectrum1653.graph fusedMap2338=true := by decide +kernel
theorem certified2338 : Certified (graph core2338) (root 10) 0 0 :=
  of_native_maps core2338 DegreeOneSmallSpectrum1647.graph DegreeOneSmallSpectrum1653.graph
    sourceMap2338 fusedMap2338 sourceMap2338_checked fusedMap2338_checked
    DegreeOneSmallComparisons.comparison2338
#print axioms sourceMap2338_checked
#print axioms fusedMap2338_checked
#print axioms certified2338
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
