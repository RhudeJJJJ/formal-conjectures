/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1910 : Family 10 := level10.get ⟨196,by decide⟩
def sourceMap1910 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (sourceLabel 10 0 0 v)
def fusedMap1910 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1910_checked : acceptsGraphIso
    (source (graph core1910) (root 10) 0 0) DegreeOneSmallSpectrum1018.graph sourceMap1910=true := by decide +kernel
theorem fusedMap1910_checked : acceptsGraphIso
    (fused (graph core1910) (root 10) 0 0) DegreeOneSmallSpectrum1021.graph fusedMap1910=true := by decide +kernel
theorem certified1910 : Certified (graph core1910) (root 10) 0 0 :=
  of_native_maps core1910 DegreeOneSmallSpectrum1018.graph DegreeOneSmallSpectrum1021.graph
    sourceMap1910 fusedMap1910 sourceMap1910_checked fusedMap1910_checked
    DegreeOneSmallComparisons.comparison1910
#print axioms sourceMap1910_checked
#print axioms fusedMap1910_checked
#print axioms certified1910
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
