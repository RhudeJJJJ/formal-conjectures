/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons09
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core169 : Family 8 := level8.get ⟨285,by decide⟩
def sourceMap169 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 8 0 1 v)
def fusedMap169 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap169_checked : acceptsGraphIso
    (source (graph core169) (root 8) 0 1) SmallGeFourSpectrum197.graph
      sourceMap169=true := by decide +kernel
theorem fusedMap169_checked : acceptsGraphIso
    (fused (graph core169) (root 8) 0 1) SmallGeFourSpectrum199.graph
      fusedMap169=true := by decide +kernel
theorem certified169 : Certified (graph core169) (root 8) 0 1 :=
  of_native_maps core169 SmallGeFourSpectrum197.graph SmallGeFourSpectrum199.graph
    sourceMap169 fusedMap169 sourceMap169_checked fusedMap169_checked
    SmallGeFourComparisons.comparison169
#print axioms sourceMap169_checked
#print axioms fusedMap169_checked
#print axioms certified169
def sourceMap169swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,9] (sourceLabel 8 1 0 v)
def fusedMap169swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap169swap_checked : acceptsGraphIso
    (source (graph core169) (root 8) 1 0) SmallGeFourSpectrum197.graph
      sourceMap169swap=true := by decide +kernel
theorem fusedMap169swap_checked : acceptsGraphIso
    (fused (graph core169) (root 8) 1 0) SmallGeFourSpectrum199.graph
      fusedMap169swap=true := by decide +kernel
theorem certified169swap : Certified (graph core169) (root 8) 1 0 :=
  of_native_maps core169 SmallGeFourSpectrum197.graph SmallGeFourSpectrum199.graph
    sourceMap169swap fusedMap169swap sourceMap169swap_checked fusedMap169swap_checked
    SmallGeFourComparisons.comparison169
#print axioms sourceMap169swap_checked
#print axioms fusedMap169swap_checked
#print axioms certified169swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
