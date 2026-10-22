/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1913 : Family 10 := level10.get ⟨1398,by decide⟩
def sourceMap1913 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,13,14,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap1913 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,6,7,8,9] (fusedLabel 10 0 2 v)
theorem sourceMap1913_checked : acceptsGraphIso
    (source (graph core1913) (root 10) 0 2) DegreeTwoThreeSpectrum3594.graph sourceMap1913=true := by decide +kernel
theorem fusedMap1913_checked : acceptsGraphIso
    (fused (graph core1913) (root 10) 0 2) DegreeTwoThreeSpectrum3609.graph fusedMap1913=true := by decide +kernel
theorem certified1913 : Certified (graph core1913) (root 10) 0 2 :=
  of_native_maps core1913 DegreeTwoThreeSpectrum3594.graph DegreeTwoThreeSpectrum3609.graph
    sourceMap1913 fusedMap1913 sourceMap1913_checked fusedMap1913_checked
    DegreeTwoThreeFiniteComparisons.comparison1913
#print axioms sourceMap1913_checked
#print axioms fusedMap1913_checked
#print axioms certified1913
def sourceMap1913swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,13,6,7,8,14] (sourceLabel 10 2 0 v)
def fusedMap1913swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,6,7,8,9] (fusedLabel 10 2 0 v)
theorem sourceMap1913swap_checked : acceptsGraphIso
    (source (graph core1913) (root 10) 2 0) DegreeTwoThreeSpectrum3594.graph sourceMap1913swap=true := by decide +kernel
theorem fusedMap1913swap_checked : acceptsGraphIso
    (fused (graph core1913) (root 10) 2 0) DegreeTwoThreeSpectrum3609.graph fusedMap1913swap=true := by decide +kernel
theorem certified1913swap : Certified (graph core1913) (root 10) 2 0 :=
  of_native_maps core1913 DegreeTwoThreeSpectrum3594.graph DegreeTwoThreeSpectrum3609.graph
    sourceMap1913swap fusedMap1913swap sourceMap1913swap_checked fusedMap1913swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1913
#print axioms sourceMap1913swap_checked
#print axioms fusedMap1913swap_checked
#print axioms certified1913swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
