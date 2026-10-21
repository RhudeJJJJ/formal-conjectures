/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2403 : Family 10 := level10.get ⟨1252,by decide⟩
def sourceMap2403 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,4,5,2,3] (sourceLabel 10 0 0 v)
def fusedMap2403 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2403_checked : acceptsGraphIso
    (source (graph core2403) (root 10) 0 0) DegreeOneSmallSpectrum1762.graph sourceMap2403=true := by decide +kernel
theorem fusedMap2403_checked : acceptsGraphIso
    (fused (graph core2403) (root 10) 0 0) DegreeOneSmallSpectrum1906.graph fusedMap2403=true := by decide +kernel
theorem certified2403 : Certified (graph core2403) (root 10) 0 0 :=
  of_native_maps core2403 DegreeOneSmallSpectrum1762.graph DegreeOneSmallSpectrum1906.graph
    sourceMap2403 fusedMap2403 sourceMap2403_checked fusedMap2403_checked
    DegreeOneSmallComparisons.comparison2403
#print axioms sourceMap2403_checked
#print axioms fusedMap2403_checked
#print axioms certified2403
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
