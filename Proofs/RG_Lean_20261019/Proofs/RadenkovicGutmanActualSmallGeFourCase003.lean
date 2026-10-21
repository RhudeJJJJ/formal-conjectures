/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons00
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core003 : Family 4 := level4.get ⟨8,by decide⟩
def sourceMap003 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 4) → Fin 10 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9] (sourceLabel 4 0 3 v)
def fusedMap003 : (Vertices 4 ⊕ Fin 5) → Fin 10 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9] (fusedLabel 4 0 3 v)
theorem sourceMap003_checked : acceptsGraphIso
    (source (graph core003) (root 4) 0 3) SmallGeFourSpectrum015.graph
      sourceMap003=true := by decide +kernel
theorem fusedMap003_checked : acceptsGraphIso
    (fused (graph core003) (root 4) 0 3) SmallGeFourSpectrum016.graph
      fusedMap003=true := by decide +kernel
theorem certified003 : Certified (graph core003) (root 4) 0 3 :=
  of_native_maps core003 SmallGeFourSpectrum015.graph SmallGeFourSpectrum016.graph
    sourceMap003 fusedMap003 sourceMap003_checked fusedMap003_checked
    SmallGeFourComparisons.comparison003
#print axioms sourceMap003_checked
#print axioms fusedMap003_checked
#print axioms certified003
def sourceMap003swap : (Vertices 4 ⊕ Fin 4 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,2,3,4,5,0,7,8,9,6] (sourceLabel 4 3 0 v)
def fusedMap003swap : (Vertices 4 ⊕ Fin 5) → Fin 10 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9] (fusedLabel 4 3 0 v)
theorem sourceMap003swap_checked : acceptsGraphIso
    (source (graph core003) (root 4) 3 0) SmallGeFourSpectrum015.graph
      sourceMap003swap=true := by decide +kernel
theorem fusedMap003swap_checked : acceptsGraphIso
    (fused (graph core003) (root 4) 3 0) SmallGeFourSpectrum016.graph
      fusedMap003swap=true := by decide +kernel
theorem certified003swap : Certified (graph core003) (root 4) 3 0 :=
  of_native_maps core003 SmallGeFourSpectrum015.graph SmallGeFourSpectrum016.graph
    sourceMap003swap fusedMap003swap sourceMap003swap_checked fusedMap003swap_checked
    SmallGeFourComparisons.comparison003
#print axioms sourceMap003swap_checked
#print axioms fusedMap003swap_checked
#print axioms certified003swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
