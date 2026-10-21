/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons07
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core124 : Family 8 := level8.get ⟨228,by decide⟩
def sourceMap124 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![4,0,1,2,3,5,6,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap124 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![4,0,1,2,3,5,6,9,10,7,8] (fusedLabel 8 0 0 v)
theorem sourceMap124_checked : acceptsGraphIso
    (source (graph core124) (root 8) 0 0) SmallGeFourSpectrum052.graph
      sourceMap124=true := by decide +kernel
theorem fusedMap124_checked : acceptsGraphIso
    (fused (graph core124) (root 8) 0 0) SmallGeFourSpectrum051.graph
      fusedMap124=true := by decide +kernel
theorem certified124 : Certified (graph core124) (root 8) 0 0 :=
  of_native_maps core124 SmallGeFourSpectrum052.graph SmallGeFourSpectrum051.graph
    sourceMap124 fusedMap124 sourceMap124_checked fusedMap124_checked
    SmallGeFourComparisons.comparison124
#print axioms sourceMap124_checked
#print axioms fusedMap124_checked
#print axioms certified124
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
