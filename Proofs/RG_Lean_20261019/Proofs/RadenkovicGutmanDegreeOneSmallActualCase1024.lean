/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1024 : Family 8 := level8.get ⟨110,by decide⟩
def sourceMap1024 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,10,8,9] (sourceLabel 8 0 1 v)
def fusedMap1024 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1024_checked : acceptsGraphIso
    (source (graph core1024) (root 8) 0 1) DegreeOneSmallSpectrum706.graph sourceMap1024=true := by decide +kernel
theorem fusedMap1024_checked : acceptsGraphIso
    (fused (graph core1024) (root 8) 0 1) DegreeOneSmallSpectrum430.graph fusedMap1024=true := by decide +kernel
theorem certified1024 : Certified (graph core1024) (root 8) 0 1 :=
  of_native_maps core1024 DegreeOneSmallSpectrum706.graph DegreeOneSmallSpectrum430.graph
    sourceMap1024 fusedMap1024 sourceMap1024_checked fusedMap1024_checked
    DegreeOneSmallComparisons.comparison1024
#print axioms sourceMap1024_checked
#print axioms fusedMap1024_checked
#print axioms certified1024
def sourceMap1024swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 8 1 0 v)
def fusedMap1024swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1024swap_checked : acceptsGraphIso
    (source (graph core1024) (root 8) 1 0) DegreeOneSmallSpectrum706.graph sourceMap1024swap=true := by decide +kernel
theorem fusedMap1024swap_checked : acceptsGraphIso
    (fused (graph core1024) (root 8) 1 0) DegreeOneSmallSpectrum430.graph fusedMap1024swap=true := by decide +kernel
theorem certified1024swap : Certified (graph core1024) (root 8) 1 0 :=
  of_native_maps core1024 DegreeOneSmallSpectrum706.graph DegreeOneSmallSpectrum430.graph
    sourceMap1024swap fusedMap1024swap sourceMap1024swap_checked fusedMap1024swap_checked
    DegreeOneSmallComparisons.comparison1024
#print axioms sourceMap1024swap_checked
#print axioms fusedMap1024swap_checked
#print axioms certified1024swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
