/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons14
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core239 : Family 9 := level9.get ⟨711,by decide⟩
def sourceMap239 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap239 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap239_checked : acceptsGraphIso
    (source (graph core239) (root 9) 0 0) SmallGeFourSpectrum227.graph
      sourceMap239=true := by decide +kernel
theorem fusedMap239_checked : acceptsGraphIso
    (fused (graph core239) (root 9) 0 0) SmallGeFourSpectrum226.graph
      fusedMap239=true := by decide +kernel
theorem certified239 : Certified (graph core239) (root 9) 0 0 :=
  of_native_maps core239 SmallGeFourSpectrum227.graph SmallGeFourSpectrum226.graph
    sourceMap239 fusedMap239 sourceMap239_checked fusedMap239_checked
    SmallGeFourComparisons.comparison239
#print axioms sourceMap239_checked
#print axioms fusedMap239_checked
#print axioms certified239
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
