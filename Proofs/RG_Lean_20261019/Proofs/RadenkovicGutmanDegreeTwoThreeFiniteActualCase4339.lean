/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4339 : Family 9 := level9.get ⟨452,by decide⟩
def sourceMap4339 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4339 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4339_checked : acceptsGraphIso
    (source (graph core4339) (root 9) 2 2) DegreeTwoThreeSpectrum4830.graph sourceMap4339=true := by decide +kernel
theorem fusedMap4339_checked : acceptsGraphIso
    (fused (graph core4339) (root 9) 2 2) DegreeTwoThreeSpectrum4469.graph fusedMap4339=true := by decide +kernel
theorem certified4339 : Certified (graph core4339) (root 9) 2 2 :=
  of_native_maps core4339 DegreeTwoThreeSpectrum4830.graph DegreeTwoThreeSpectrum4469.graph
    sourceMap4339 fusedMap4339 sourceMap4339_checked fusedMap4339_checked
    DegreeTwoThreeFiniteComparisons.comparison4339
#print axioms sourceMap4339_checked
#print axioms fusedMap4339_checked
#print axioms certified4339
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
