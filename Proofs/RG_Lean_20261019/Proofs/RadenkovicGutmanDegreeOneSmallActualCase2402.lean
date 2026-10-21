/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2402 : Family 10 := level10.get ⟨1250,by decide⟩
def sourceMap2402 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (sourceLabel 10 0 0 v)
def fusedMap2402 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2402_checked : acceptsGraphIso
    (source (graph core2402) (root 10) 0 0) DegreeOneSmallSpectrum1819.graph sourceMap2402=true := by decide +kernel
theorem fusedMap2402_checked : acceptsGraphIso
    (fused (graph core2402) (root 10) 0 0) DegreeOneSmallSpectrum1903.graph fusedMap2402=true := by decide +kernel
theorem certified2402 : Certified (graph core2402) (root 10) 0 0 :=
  of_native_maps core2402 DegreeOneSmallSpectrum1819.graph DegreeOneSmallSpectrum1903.graph
    sourceMap2402 fusedMap2402 sourceMap2402_checked fusedMap2402_checked
    DegreeOneSmallComparisons.comparison2402
#print axioms sourceMap2402_checked
#print axioms fusedMap2402_checked
#print axioms certified2402
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
