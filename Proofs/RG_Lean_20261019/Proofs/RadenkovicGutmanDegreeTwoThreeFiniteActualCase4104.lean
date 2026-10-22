/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4104 : Family 8 := level8.get ⟨38,by decide⟩
def sourceMap4104 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap4104 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4104_checked : acceptsGraphIso
    (source (graph core4104) (root 8) 2 2) DegreeTwoThreeSpectrum3146.graph sourceMap4104=true := by decide +kernel
theorem fusedMap4104_checked : acceptsGraphIso
    (fused (graph core4104) (root 8) 2 2) DegreeTwoThreeSpectrum2318.graph fusedMap4104=true := by decide +kernel
theorem certified4104 : Certified (graph core4104) (root 8) 2 2 :=
  of_native_maps core4104 DegreeTwoThreeSpectrum3146.graph DegreeTwoThreeSpectrum2318.graph
    sourceMap4104 fusedMap4104 sourceMap4104_checked fusedMap4104_checked
    DegreeTwoThreeFiniteComparisons.comparison4104
#print axioms sourceMap4104_checked
#print axioms fusedMap4104_checked
#print axioms certified4104
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
