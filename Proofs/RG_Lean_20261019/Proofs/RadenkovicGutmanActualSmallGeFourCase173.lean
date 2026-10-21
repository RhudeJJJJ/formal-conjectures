/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons10
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core173 : Family 9 := level9.get ⟨286,by decide⟩
def sourceMap173 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap173 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,4,5,6,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap173_checked : acceptsGraphIso
    (source (graph core173) (root 9) 0 0) SmallGeFourSpectrum128.graph
      sourceMap173=true := by decide +kernel
theorem fusedMap173_checked : acceptsGraphIso
    (fused (graph core173) (root 9) 0 0) SmallGeFourSpectrum103.graph
      fusedMap173=true := by decide +kernel
theorem certified173 : Certified (graph core173) (root 9) 0 0 :=
  of_native_maps core173 SmallGeFourSpectrum128.graph SmallGeFourSpectrum103.graph
    sourceMap173 fusedMap173 sourceMap173_checked fusedMap173_checked
    SmallGeFourComparisons.comparison173
#print axioms sourceMap173_checked
#print axioms fusedMap173_checked
#print axioms certified173
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
