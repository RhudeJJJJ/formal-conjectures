/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2416 : Family 10 := level10.get ⟨1297,by decide⟩
def sourceMap2416 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,12,2,3] (sourceLabel 10 0 0 v)
def fusedMap2416 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2416_checked : acceptsGraphIso
    (source (graph core2416) (root 10) 0 0) DegreeOneSmallSpectrum1860.graph sourceMap2416=true := by decide +kernel
theorem fusedMap2416_checked : acceptsGraphIso
    (fused (graph core2416) (root 10) 0 0) DegreeOneSmallSpectrum1934.graph fusedMap2416=true := by decide +kernel
theorem certified2416 : Certified (graph core2416) (root 10) 0 0 :=
  of_native_maps core2416 DegreeOneSmallSpectrum1860.graph DegreeOneSmallSpectrum1934.graph
    sourceMap2416 fusedMap2416 sourceMap2416_checked fusedMap2416_checked
    DegreeOneSmallComparisons.comparison2416
#print axioms sourceMap2416_checked
#print axioms fusedMap2416_checked
#print axioms certified2416
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
