/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons06
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core110 : Family 8 := level8.get ⟨131,by decide⟩
def sourceMap110 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,2,3,4,5,6] (sourceLabel 8 0 0 v)
def fusedMap110 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,8,9,10,6,7] (fusedLabel 8 0 0 v)
theorem sourceMap110_checked : acceptsGraphIso
    (source (graph core110) (root 8) 0 0) SmallGeFourSpectrum042.graph
      sourceMap110=true := by decide +kernel
theorem fusedMap110_checked : acceptsGraphIso
    (fused (graph core110) (root 8) 0 0) SmallGeFourSpectrum053.graph
      fusedMap110=true := by decide +kernel
theorem certified110 : Certified (graph core110) (root 8) 0 0 :=
  of_native_maps core110 SmallGeFourSpectrum042.graph SmallGeFourSpectrum053.graph
    sourceMap110 fusedMap110 sourceMap110_checked fusedMap110_checked
    SmallGeFourComparisons.comparison110
#print axioms sourceMap110_checked
#print axioms fusedMap110_checked
#print axioms certified110
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
