/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1761 : Family 9 := level9.get ⟨634,by decide⟩
def sourceMap1761 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,2,3] (sourceLabel 9 0 0 v)
def fusedMap1761 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1761_checked : acceptsGraphIso
    (source (graph core1761) (root 9) 0 0) SmallGeFourSpectrum227.graph sourceMap1761=true := by decide +kernel
theorem fusedMap1761_checked : acceptsGraphIso
    (fused (graph core1761) (root 9) 0 0) SmallGeFourSpectrum167.graph fusedMap1761=true := by decide +kernel
theorem certified1761 : Certified (graph core1761) (root 9) 0 0 :=
  of_native_maps core1761 SmallGeFourSpectrum227.graph SmallGeFourSpectrum167.graph
    sourceMap1761 fusedMap1761 sourceMap1761_checked fusedMap1761_checked
    DegreeOneSmallComparisons.comparison1761
#print axioms sourceMap1761_checked
#print axioms fusedMap1761_checked
#print axioms certified1761
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
