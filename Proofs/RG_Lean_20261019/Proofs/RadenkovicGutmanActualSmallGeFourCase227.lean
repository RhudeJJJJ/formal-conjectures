/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons13
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core227 : Family 9 := level9.get ⟨687,by decide⟩
def sourceMap227 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,9,10,11,1,2,3,4,5,6,7,8] (sourceLabel 9 0 0 v)
def fusedMap227 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,9,10,11,1,2,5,6,7,8,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap227_checked : acceptsGraphIso
    (source (graph core227) (root 9) 0 0) SmallGeFourSpectrum178.graph
      sourceMap227=true := by decide +kernel
theorem fusedMap227_checked : acceptsGraphIso
    (fused (graph core227) (root 9) 0 0) SmallGeFourSpectrum167.graph
      fusedMap227=true := by decide +kernel
theorem certified227 : Certified (graph core227) (root 9) 0 0 :=
  of_native_maps core227 SmallGeFourSpectrum178.graph SmallGeFourSpectrum167.graph
    sourceMap227 fusedMap227 sourceMap227_checked fusedMap227_checked
    SmallGeFourComparisons.comparison227
#print axioms sourceMap227_checked
#print axioms fusedMap227_checked
#print axioms certified227
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
