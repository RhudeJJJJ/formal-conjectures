/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons06
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core108 : Family 8 := level8.get ⟨94,by decide⟩
def sourceMap108 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,8,9,10,3,4,5,6,7] (sourceLabel 8 0 0 v)
def fusedMap108 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,4,5,6,2,3] (fusedLabel 8 0 0 v)
theorem sourceMap108_checked : acceptsGraphIso
    (source (graph core108) (root 8) 0 0) SmallGeFourSpectrum044.graph
      sourceMap108=true := by decide +kernel
theorem fusedMap108_checked : acceptsGraphIso
    (fused (graph core108) (root 8) 0 0) SmallGeFourSpectrum038.graph
      fusedMap108=true := by decide +kernel
theorem certified108 : Certified (graph core108) (root 8) 0 0 :=
  of_native_maps core108 SmallGeFourSpectrum044.graph SmallGeFourSpectrum038.graph
    sourceMap108 fusedMap108 sourceMap108_checked fusedMap108_checked
    SmallGeFourComparisons.comparison108
#print axioms sourceMap108_checked
#print axioms fusedMap108_checked
#print axioms certified108
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
