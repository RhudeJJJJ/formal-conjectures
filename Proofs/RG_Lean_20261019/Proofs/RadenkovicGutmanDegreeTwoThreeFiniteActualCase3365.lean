/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3365 : Family 9 := level9.get ⟨407,by decide⟩
def sourceMap3365 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3365 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3365_checked : acceptsGraphIso
    (source (graph core3365) (root 9) 0 5) DegreeTwoThreeSpectrum6429.graph sourceMap3365=true := by decide +kernel
theorem fusedMap3365_checked : acceptsGraphIso
    (fused (graph core3365) (root 9) 0 5) DegreeTwoThreeSpectrum5363.graph fusedMap3365=true := by decide +kernel
theorem certified3365 : Certified (graph core3365) (root 9) 0 5 :=
  of_native_maps core3365 DegreeTwoThreeSpectrum6429.graph DegreeTwoThreeSpectrum5363.graph
    sourceMap3365 fusedMap3365 sourceMap3365_checked fusedMap3365_checked
    DegreeTwoThreeFiniteComparisons.comparison3365
#print axioms sourceMap3365_checked
#print axioms fusedMap3365_checked
#print axioms certified3365
def sourceMap3365swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3365swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3365swap_checked : acceptsGraphIso
    (source (graph core3365) (root 9) 5 0) DegreeTwoThreeSpectrum6429.graph sourceMap3365swap=true := by decide +kernel
theorem fusedMap3365swap_checked : acceptsGraphIso
    (fused (graph core3365) (root 9) 5 0) DegreeTwoThreeSpectrum5363.graph fusedMap3365swap=true := by decide +kernel
theorem certified3365swap : Certified (graph core3365) (root 9) 5 0 :=
  of_native_maps core3365 DegreeTwoThreeSpectrum6429.graph DegreeTwoThreeSpectrum5363.graph
    sourceMap3365swap fusedMap3365swap sourceMap3365swap_checked fusedMap3365swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3365
#print axioms sourceMap3365swap_checked
#print axioms fusedMap3365swap_checked
#print axioms certified3365swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
