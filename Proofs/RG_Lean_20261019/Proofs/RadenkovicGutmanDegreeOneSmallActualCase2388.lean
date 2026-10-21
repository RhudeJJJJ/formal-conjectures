/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2388 : Family 10 := level10.get ⟨1182,by decide⟩
def sourceMap2388 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2388 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,12,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap2388_checked : acceptsGraphIso
    (source (graph core2388) (root 10) 0 0) DegreeOneSmallSpectrum1881.graph sourceMap2388=true := by decide +kernel
theorem fusedMap2388_checked : acceptsGraphIso
    (fused (graph core2388) (root 10) 0 0) DegreeOneSmallSpectrum1877.graph fusedMap2388=true := by decide +kernel
theorem certified2388 : Certified (graph core2388) (root 10) 0 0 :=
  of_native_maps core2388 DegreeOneSmallSpectrum1881.graph DegreeOneSmallSpectrum1877.graph
    sourceMap2388 fusedMap2388 sourceMap2388_checked fusedMap2388_checked
    DegreeOneSmallComparisons.comparison2388
#print axioms sourceMap2388_checked
#print axioms fusedMap2388_checked
#print axioms certified2388
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
