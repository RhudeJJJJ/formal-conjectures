/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1920 : Family 10 := level10.get ⟨208,by decide⟩
def sourceMap1920 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,6,0,1,2,3,4,5,12,11,9,10] (sourceLabel 10 0 0 v)
def fusedMap1920 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1920_checked : acceptsGraphIso
    (source (graph core1920) (root 10) 0 0) DegreeOneSmallSpectrum1062.graph sourceMap1920=true := by decide +kernel
theorem fusedMap1920_checked : acceptsGraphIso
    (fused (graph core1920) (root 10) 0 0) DegreeOneSmallSpectrum1080.graph fusedMap1920=true := by decide +kernel
theorem certified1920 : Certified (graph core1920) (root 10) 0 0 :=
  of_native_maps core1920 DegreeOneSmallSpectrum1062.graph DegreeOneSmallSpectrum1080.graph
    sourceMap1920 fusedMap1920 sourceMap1920_checked fusedMap1920_checked
    DegreeOneSmallComparisons.comparison1920
#print axioms sourceMap1920_checked
#print axioms fusedMap1920_checked
#print axioms certified1920
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
