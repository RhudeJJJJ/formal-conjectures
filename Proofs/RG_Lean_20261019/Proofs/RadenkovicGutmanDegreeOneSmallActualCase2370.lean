/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2370 : Family 10 := level10.get ⟨1130,by decide⟩
def sourceMap2370 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2370 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2370_checked : acceptsGraphIso
    (source (graph core2370) (root 10) 0 0) DegreeOneSmallSpectrum1784.graph sourceMap2370=true := by decide +kernel
theorem fusedMap2370_checked : acceptsGraphIso
    (fused (graph core2370) (root 10) 0 0) DegreeOneSmallSpectrum1793.graph fusedMap2370=true := by decide +kernel
theorem certified2370 : Certified (graph core2370) (root 10) 0 0 :=
  of_native_maps core2370 DegreeOneSmallSpectrum1784.graph DegreeOneSmallSpectrum1793.graph
    sourceMap2370 fusedMap2370 sourceMap2370_checked fusedMap2370_checked
    DegreeOneSmallComparisons.comparison2370
#print axioms sourceMap2370_checked
#print axioms fusedMap2370_checked
#print axioms certified2370
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
