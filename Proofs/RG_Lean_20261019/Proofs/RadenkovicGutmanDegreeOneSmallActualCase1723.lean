/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1723 : Family 9 := level9.get ⟨542,by decide⟩
def sourceMap1723 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (sourceLabel 9 0 0 v)
def fusedMap1723 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1723_checked : acceptsGraphIso
    (source (graph core1723) (root 9) 0 0) SmallGeFourSpectrum201.graph sourceMap1723=true := by decide +kernel
theorem fusedMap1723_checked : acceptsGraphIso
    (fused (graph core1723) (root 9) 0 0) SmallGeFourSpectrum112.graph fusedMap1723=true := by decide +kernel
theorem certified1723 : Certified (graph core1723) (root 9) 0 0 :=
  of_native_maps core1723 SmallGeFourSpectrum201.graph SmallGeFourSpectrum112.graph
    sourceMap1723 fusedMap1723 sourceMap1723_checked fusedMap1723_checked
    DegreeOneSmallComparisons.comparison1723
#print axioms sourceMap1723_checked
#print axioms fusedMap1723_checked
#print axioms certified1723
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
