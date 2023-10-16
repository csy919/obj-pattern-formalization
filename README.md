# obj-pattern-formalization

This archive provides the formalization for the technical content of Section 3, Section 4, and Section 5 for the article "Refinement Verification of OS Services based on a Verified Preemptive Microkernel".

\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

The extensions to the verification framework of CSL-R (Section 3 of the article) are explained as follows. 

The modified type for atomic options in the specification language is "Definition osabstep" in framework/model/language.v

The semantics of the extended specification language is given by "Inductive spec_step" in framework/model/opsem.v 

The added rule for the program logic about the "ABORT" statement is given by the constructor absabort_rule of "Inductive InfRules" in framework/logic/inferules.v

The semantic rule for calls to functions with abstract specification is captured by the constructor hapienter_step of "Inductive hapistep" in framework/model/opsem.v

The modified construction of pre/post-conditions for API functions is given by "Definition BuildPreA'" in framework/logic/inferules.v

The modified simulation conditions catering for assumptions about the user are given in 
framework/proof/simulation.v

The soundness of the framework is established mainly in the following two files
framework/proof/soundness.v
framework/proof/toptheorem.v

=================================================

For Section 4 of the paper, the struct for service object is formalized in "Definition service_obj_t" in certiucos/code/os_ucos_h.v

The definition of abstract service objects is "Module absobj" in framework/model/language.v

The definition of sobjmp (the function from indices to optional abstract service objects) is ObjMap in framework/model/language.v

The condition sobj_kobj_ref corresponds to "Definition RH_OBJ_ECB_P" in certiucos/spec/os_inv.v 

(in this formalization, the kernel objects discussed in the article take the concrete form of the event control blocks for the semaphores of uC/OS-II)

The condition kobj_ref_distinct corresponds to "Definition objref_distinct" in certiucos/spec/os_inv.v

The invariant condition sobj_kobj_aux in Section 5 corresponds to "Definition OBJ_AUX_P" in certiucos/spec/os_inv.v

=================================================

The code patterns for the functions about the creation/deletion/use of service objects, and about the creation/deletion/use of kernel objects, are formalized in the following files. 

certiucos/code/obj/service_obj_create.v
certiucos/code/obj/service_obj_delete.v
certiucos/code/obj/service_obj_oper.v

certiucos/code/obj/kernel_obj_create.v
certiucos/code/obj/kernel_obj_delete.v
certiucos/code/obj/kernel_obj_oper.v

The specifications for the functions about the creation/deletion/use of service objects, and about the creation/deletion/use of kernel objects, are given in the following files. 

certiucos/spec/obj/service_obj_create_spec.v (Definition sobjcre)
certiucos/spec/obj/service_obj_delete_spec.v (Definition sobjdel)
certiucos/spec/obj/service_obj_oper_spec.v (Definition sobjoper)

certiucos/spec/obj/kernel_obj_create_spec.v (KObjCreatePre' and KObjCreatePost')
certiucos/spec/obj/kernel_obj_delete_spec.v (KObjDelPre' and KObjDelPost')
certiucos/spec/obj/kernel_obj_oper_spec.v (KObjOperPre' and KObjOperPost')

The proofs for the functions about the creation/deletion/use of service objects, and about the creation/deletion/use of kernel objects, are formalized in the following files. 

certiucos/proofs/obj/service_obj_create_proof.v
certiucos/proofs/obj/service_obj_delete_proof.v
certiucos/proofs/obj/service_obj_oper_proof.v

certiucos/proofs/obj/kernel_obj_create_proof.v
certiucos/proofs/obj/kernel_obj_delete_proof.v
certiucos/proofs/obj/kernel_obj_oper_proof.v

The formalized code, specification and proof for the internal function get_free_obj is given in the following files.

certiucos/code/obj/get_free_obj_idx.v
certiucos/spec/obj/get_free_obj_idx_spec.v 
certiucos/proofs/obj/get_free_obj_idx_proof.v 

There are a number of files containing the auxiliary lemmas and tactics for the verification of the code patterns. Part of these files have paths in the following list. 

certiucos/ucos_lib/obj/Aarray_new_common.v
certiucos/ucos_lib/obj/Aarray_new_common_extend.v
certiucos/ucos_lib/obj/obj_common.v                
certiucos/ucos_lib/obj/obj_common_ext.v           
certiucos/ucos_lib/obj/objauxvar_lemmas.v
certiucos/ucos_lib/obj/objaux_pure.v

tactics/hoareforward/hoare_assign_tac_ext.v

/////////////////////////////////////////////////

The formal verification of the service and kernel functions for object creation/deletion/use mainly illustrates: 
- how our extension to the verification framework of CSL-R supports the compositional specification of the functions implementing a service
- how the design of invariants helps establish desired properties about the connection of service objects to kernel objects
- how the code patterns for a generic form of a service (consisting of object creation/deletion/use) is verified

Our formal verification of the inter-task communication services extending the mutexes, semaphores and message queues of uC/OS-II (Section 6 of the paper) targets concrete implementations of the three services, instead of the generic code patterns in this formalization. 
