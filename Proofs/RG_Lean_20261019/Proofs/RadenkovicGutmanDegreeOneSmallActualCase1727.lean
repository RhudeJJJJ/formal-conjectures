/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1727 : Family 9 := level9.get ⟨545,by decide⟩
def sourceMap1727 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,8,9] (sourceLabel 9 0 0 v)
def fusedMap1727 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1727_checked : acceptsGraphIso
    (source (graph core1727) (root 9) 0 0) SmallGeFourSpectrum211.graph sourceMap1727=true := by decide +kernel
theorem fusedMap1727_checked : acceptsGraphIso
    (fused (graph core1727) (root 9) 0 0) SmallGeFourSpectrum117.graph fusedMap1727=true := by decide +kernel
theorem certified1727 : Certified (graph core1727) (root 9) 0 0 :=
  of_native_maps core1727 SmallGeFourSpectrum211.graph SmallGeFourSpectrum117.graph
    sourceMap1727 fusedMap1727 sourceMap1727_checked fusedMap1727_checked
    DegreeOneSmallComparisons.comparison1727
#print axioms sourceMap1727_checked
#print axioms fusedMap1727_checked
#print axioms certified1727
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
