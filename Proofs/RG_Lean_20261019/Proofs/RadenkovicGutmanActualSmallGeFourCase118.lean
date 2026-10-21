/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons06
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core118 : Family 8 := level8.get ⟨187,by decide⟩
def sourceMap118 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,8,9,10,2,3,4,5,6,7] (sourceLabel 8 0 0 v)
def fusedMap118 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,8,9,10,4,5,6,7,2,3] (fusedLabel 8 0 0 v)
theorem sourceMap118_checked : acceptsGraphIso
    (source (graph core118) (root 8) 0 0) SmallGeFourSpectrum040.graph
      sourceMap118=true := by decide +kernel
theorem fusedMap118_checked : acceptsGraphIso
    (fused (graph core118) (root 8) 0 0) SmallGeFourSpectrum062.graph
      fusedMap118=true := by decide +kernel
theorem certified118 : Certified (graph core118) (root 8) 0 0 :=
  of_native_maps core118 SmallGeFourSpectrum040.graph SmallGeFourSpectrum062.graph
    sourceMap118 fusedMap118 sourceMap118_checked fusedMap118_checked
    SmallGeFourComparisons.comparison118
#print axioms sourceMap118_checked
#print axioms fusedMap118_checked
#print axioms certified118
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
