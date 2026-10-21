/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1840 : Family 10 := level10.get ⟨91,by decide⟩
def sourceMap1840 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1840 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1840_checked : acceptsGraphIso
    (source (graph core1840) (root 10) 0 0) DegreeOneSmallSpectrum1166.graph sourceMap1840=true := by decide +kernel
theorem fusedMap1840_checked : acceptsGraphIso
    (fused (graph core1840) (root 10) 0 0) DegreeOneSmallSpectrum913.graph fusedMap1840=true := by decide +kernel
theorem certified1840 : Certified (graph core1840) (root 10) 0 0 :=
  of_native_maps core1840 DegreeOneSmallSpectrum1166.graph DegreeOneSmallSpectrum913.graph
    sourceMap1840 fusedMap1840 sourceMap1840_checked fusedMap1840_checked
    DegreeOneSmallComparisons.comparison1840
#print axioms sourceMap1840_checked
#print axioms fusedMap1840_checked
#print axioms certified1840
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
