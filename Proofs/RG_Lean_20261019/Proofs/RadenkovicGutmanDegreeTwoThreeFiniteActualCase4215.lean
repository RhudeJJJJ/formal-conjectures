/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4215 : Family 9 := level9.get ⟨106,by decide⟩
def sourceMap4215 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,8,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4215 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 2 2 v)
theorem sourceMap4215_checked : acceptsGraphIso
    (source (graph core4215) (root 9) 2 2) DegreeTwoThreeSpectrum4552.graph sourceMap4215=true := by decide +kernel
theorem fusedMap4215_checked : acceptsGraphIso
    (fused (graph core4215) (root 9) 2 2) DegreeTwoThreeSpectrum4103.graph fusedMap4215=true := by decide +kernel
theorem certified4215 : Certified (graph core4215) (root 9) 2 2 :=
  of_native_maps core4215 DegreeTwoThreeSpectrum4552.graph DegreeTwoThreeSpectrum4103.graph
    sourceMap4215 fusedMap4215 sourceMap4215_checked fusedMap4215_checked
    DegreeTwoThreeFiniteComparisons.comparison4215
#print axioms sourceMap4215_checked
#print axioms fusedMap4215_checked
#print axioms certified4215
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
