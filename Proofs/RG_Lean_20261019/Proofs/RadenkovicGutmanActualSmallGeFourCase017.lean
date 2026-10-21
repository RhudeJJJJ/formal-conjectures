/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons01
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core017 : Family 5 := level5.get ⟨18,by decide⟩
def sourceMap017 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,7,8,9,3,4,5,6] (sourceLabel 5 1 1 v)
def fusedMap017 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9] (fusedLabel 5 1 1 v)
theorem sourceMap017_checked : acceptsGraphIso
    (source (graph core017) (root 5) 1 1) SmallGeFourSpectrum034.graph
      sourceMap017=true := by decide +kernel
theorem fusedMap017_checked : acceptsGraphIso
    (fused (graph core017) (root 5) 1 1) SmallGeFourSpectrum022.graph
      fusedMap017=true := by decide +kernel
theorem certified017 : Certified (graph core017) (root 5) 1 1 :=
  of_native_maps core017 SmallGeFourSpectrum034.graph SmallGeFourSpectrum022.graph
    sourceMap017 fusedMap017 sourceMap017_checked fusedMap017_checked
    SmallGeFourComparisons.comparison017
#print axioms sourceMap017_checked
#print axioms fusedMap017_checked
#print axioms certified017
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
