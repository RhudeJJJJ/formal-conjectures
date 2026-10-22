/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1007 : Family 10 := level10.get ⟨1738,by decide⟩
def sourceMap1007 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap1007 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,5,6,7,8,9,10,11,12,1,2,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap1007_checked : acceptsGraphIso
    (source (graph core1007) (root 10) 0 0) DegreeTwoThreeSpectrum1633.graph sourceMap1007=true := by decide +kernel
theorem fusedMap1007_checked : acceptsGraphIso
    (fused (graph core1007) (root 10) 0 0) DegreeOneSmallSpectrum1917.graph fusedMap1007=true := by decide +kernel
theorem certified1007 : Certified (graph core1007) (root 10) 0 0 :=
  of_native_maps core1007 DegreeTwoThreeSpectrum1633.graph DegreeOneSmallSpectrum1917.graph
    sourceMap1007 fusedMap1007 sourceMap1007_checked fusedMap1007_checked
    DegreeTwoThreeFiniteComparisons.comparison1007
#print axioms sourceMap1007_checked
#print axioms fusedMap1007_checked
#print axioms certified1007
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
